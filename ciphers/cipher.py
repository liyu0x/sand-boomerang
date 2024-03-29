'''
Created on Mar 25, 2014

@author: stefan
'''

from abc import ABCMeta, abstractmethod


class AbstractCipher(object, metaclass=ABCMeta):
    """
    Abstract Class for Ciphers
    """

    @abstractmethod
    def createSTP(self, filename, cipherParameters):
        """
        Each cipher need to define how it creates an instance for the
        SMT solver.
        """
        pass

    @abstractmethod
    def getFormatString(self):
        """
        Each cipher needs to specify the format it should be printed.
        """
        pass

    @abstractmethod
    def create_cluster_parameters(self, parameters, characteristics):
        pass

    @abstractmethod
    def get_diff_hex(self, parameters, characteristics):
        pass

    # @abstractmethod
    # def get_cluster_params(self, parameters):
    #     pass